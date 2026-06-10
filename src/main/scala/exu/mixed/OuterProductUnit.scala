package saturn.exu

import chisel3._
import chisel3.util._
import org.chipsalliance.cde.config._
import freechips.rocketchip.rocket._
import freechips.rocketchip.util._
import freechips.rocketchip.tile._
import chisel3.util.experimental.decode._
import saturn.common._
import saturn.backend._
import hardfloat._
import scala.math._

// Declare supported types (dictates multipler instantiated)
object OPUTypes extends Enumeration { val INT32, INT16, INT8 = Value }

// Parameters for configured OPU
case class OPUParameters (
  val aWidth : Int = 8,
  val bWidth : Int = 8,
  val cWidth : Int = 32, // Accumulator size

  val nMrfRegs : Int = 2
)

trait HasOPUParams extends HasVectorParams { this: HasCoreParameters =>
  def varchRatio = vLen / dLen
  def regsPerTileReg = varchRatio * varchRatio
  def regsPerCell = regsPerTileReg * opuParams.nMrfRegs
  def cellRegIdxBits = log2Ceil(regsPerCell)
  def prodWidth = opuParams.aWidth + opuParams.bWidth

  def wideningFactor = opuParams.cWidth / opuParams.aWidth

  def clusterXdim = opuParams.cWidth / opuParams.bWidth
  def clusterYdim = clusterXdim

  def yDim = (dLen / opuParams.aWidth) / clusterYdim
  def xDim = (dLen / opuParams.bWidth) / clusterXdim

  def max_kfactor = 1 // Maximum allowable kfactor

}


/*
 * A single cell in the Outer Product Unit MACC array
 * Accumulation register alse serve as pipeline registers
 * during read out
 */
class OuterProductCell(implicit p: Parameters) extends CoreModule()(p) with HasOPUParams {

  val io = IO(new Bundle{
    // Data signals
    val in_l = Input(SInt(opuParams.aWidth.W)) // left input
    val in_t = Input(SInt(opuParams.bWidth.W)) // top input

    // Contol Signals
    val mrf_idx = Input(UInt(cellRegIdxBits.W)) // Index for µarch register to write

    val intra_k_reduce = Input(Bool())
    val inter_k_reduce = Input(Bool())

    val macc = Input(Bool())
    val mvin = Input(Bool())
    val mvin_bcast = Input(Bool())
    val mvin_data = Input(SInt(opuParams.cWidth.W))
    val out = Output(SInt(opuParams.cWidth.W))
  })
  // Matrix Register + Logic
  val regs = Reg(Vec(regsPerCell, SInt(opuParams.cWidth.W)))

  // TODO: Need to check for overflow and saturate to accumulator width
  val prod = Mux(io.macc, io.in_l * io.in_t, 0.S)
  val sum = prod + regs(io.mrf_idx)   // Original

  // For inner k greater than 1
  val k_reduce = io.intra_k_reduce || io.inter_k_reduce
  val intra_reg_ind = mrf_idx + (varchRatio + 1).U;

  // Selection for adder (mux can be optimized away if max_kfactor = 1, 
  // be driving constants to inputs)
  // May be able to reuse io.mvin for io.inter_k_reduce
  val add_op = Mux(io.intra_k_reduce, regs(intra_reg_ind), 
               Mux(io.inter_k_reduce, io.mvin_data,
                                      prod))

  val sum = regs(io.mrf_idx) + add_op // If using k_factor reduce


  // Data going into MRF
  for (i <- 0 until regsPerCell) {
    val tile_match = (io.mrf_idx >> log2Ceil(regsPerTileReg)) === (i >> log2Ceil(regsPerTileReg)).U
    val subtile_match = io.mrf_idx(log2Ceil(regsPerTileReg)-1,0) === (i % regsPerTileReg).U

    when (tile_match && (((io.mvin || io.macc || k_reduce) && subtile_match) || io.mvin_bcast)) {
      regs(i) := Mux(io.macc, sum, io.mvin_data)
    }
  }

  io.out := regs(io.mrf_idx)
}

class OuterProductCluster(row: Int, col: Int)(implicit p : Parameters) extends CoreModule()(p) with HasOPUParams {
  // val pass_pipes = 1
  val pass_pipes = 2 if max_kfactor > 2 else 1  // Hardcoded
  // val pass_pipes = clusterXdim/2 if max_kfactor > 2 else 1 // clusterXdim/2 represents the max number of pipes you would want to move simultaneously

  val io = IO(new Bundle{
    val in_l      = Input(Vec(clusterYdim, UInt(opuParams.aWidth.W)))
    val in_t      = Input(Vec(clusterXdim, UInt(opuParams.bWidth.W)))

    val in_pipe   = Input(Vec(pass_pipes, UInt(opuParams.cWidth.W)))
    val out_pipe  = Output(Vec(pass_pipes, UInt(opuParams.cWidth.W)))

    // val k_reduce  = Input(Bool()) // Indicates that you should be reducing with input for k factor reduction
    val k_reduce  = Input(UInt(2.W))  // 0 -> k=1, 1 -> k=2, 2 -> k=4 (i.e. k=2^k_reduce)

    val mrf_idx = Input(UInt(cellRegIdxBits.W))
    val row_idx = Input(UInt(log2Ceil(clusterYdim).W))
    val col_idx = Input(UInt(log2Ceil(clusterXdim).W))

    val macc  = Input(Bool())
    val shift = Input(Bool())
    val mvin  = Input(Bool())
    val mvin_bcast = Input(Bool())
  })

  val cells = Seq.fill(clusterXdim, clusterYdim)(Module(new OuterProductCell))
  val cell_outs = Wire(Vec(clusterYdim, Vec(clusterXdim, UInt(opuParams.cWidth.W))))
  val pipe = Reg(Vec(pass_pipes, UInt(opuParams.cWidth.W)))

  for (i <- 0 until clusterYdim) {
    for (j <- 0 until clusterXdim) {
      val cell = cells(i)(j)

      cell.io.inter_k_reduce := k_reduce(0)
      cell.io.intra_k_reduce := k_reduce(1)

      cell.io.in_l  := io.in_l(i).asSInt
      cell.io.in_t  := io.in_t(j).asSInt

      cell.io.macc := io.macc
      cell.io.mvin := io.mvin && i.U === io.row_idx && j.U === io.col_idx
      cell.io.mvin_bcast := io.mvin_bcast && j.U === io.col_idx
      // cell.io.mvin_data := io.in_t.asUInt.asSInt
      cell.io.mrf_idx := io.mrf_idx
      cell_outs(i)(j) := cell.io.out.asUInt
      cell.io.mvin_data := MuxLookup( k_reduce, 
                                      io.in_t.asUInt.asSInt, 
                                      Seq(
                                        0.U -> io.in_t.asUInt.asSInt,
                                        1.U -> io.in_pipe(0),
                                        2.U -> io.in_pipe(1)
                                      ))
    }
  }



  pipe(0) := Mux(io.shift, io.in_pipe(0), cell_outs(io.row_idx)(io.col_idx))
  io.out_pipe(0) := pipe(0)

  // For k=2 need to shift two columns
  // Secondary input, output ports for this case
  if (max_kfactor >= 2) {
    pipe(1) := Mux(io.shift, io.in_pipe(1), cell_outs(io.row_idx)(io.col_idx+1)) // Plus 1 should be truncated by the bit width
    io.out_pipe(1) := pipe(1)
  } 

}

class OuterProductControl(implicit p: Parameters) extends CoreBundle()(p) with HasOPUParams {
  val clock_enable = Bool()

  val in_l      = Vec(yDim, Vec(clusterYdim, UInt(opuParams.aWidth.W)))
  val in_t      = Vec(xDim, Vec(clusterXdim, UInt(opuParams.bWidth.W)))

  // same values broadcast horizontally
  val mrf_idx    = Vec(yDim, UInt(cellRegIdxBits.W))
  val row_idx    = Vec(yDim, UInt(log2Ceil(clusterYdim).W))
  val col_idx    = Vec(yDim, UInt(log2Ceil(clusterXdim).W))
  val macc       = Vec(yDim, Bool())
  val mvin       = Vec(yDim, Bool())
  val mvin_bcast = Vec(yDim, Bool())
  val shift      = Vec(yDim, Bool())
  val k_reduce   = Vec(yDim, Bool())
}


class OuterProductUnit(implicit p: Parameters) extends CoreModule()(p) with HasOPUParams {
  val io = IO(new Bundle {
    val op = Input(new OuterProductControl)
    val out = Output(Vec(xDim, UInt(opuParams.cWidth.W)))
    val YOU_SHALL_PASS = Output(Bool())
  })

  // clock gating
  val gated_clock = ClockGate(clock, io.op.clock_enable, "opu_clock_gate")

  // Force OuterProductUnit to have logic to be syn-mappable
  io.YOU_SHALL_PASS := io.op.macc(0) & io.op.macc(0) | io.op.shift(0)
  dontTouch(io.YOU_SHALL_PASS)

  val clusters = Seq.fill(yDim, xDim)(withClock(gated_clock) { Module(new OuterProductCluster) })

  for (j <- 0 until xDim) {
    for (i <- 0 until yDim) {
      val cluster = clusters(i)(j)
      cluster.io.in_l      := io.op.in_l(i)
      cluster.io.in_t      := io.op.in_t(j)

      cluster.io.mrf_idx    := io.op.mrf_idx(i)
      cluster.io.row_idx    := io.op.row_idx(i)
      cluster.io.col_idx    := io.op.col_idx(i)
      cluster.io.macc       := io.op.macc(i)
      cluster.io.mvin       := io.op.mvin(i)
      cluster.io.mvin_bcast := io.op.mvin_bcast(i)
      cluster.io.shift      := io.op.shift(i)
    }

    clusters(0)(j).io.in_pipe := 0.U
    for (i <- 1 until yDim) {
      clusters(i)(j).io.in_pipe(0) := clusters(i-1)(j).io.out_pipe(0)
      if (max_kfactor > 1) {
        clusters(i)(j).io.in_pipe(1) := clusters(i-1)(j).io.out_pipe(1)
      }
    }
    io.out(j) := clusters(yDim-1)(j).io.out_pipe
  }
}
