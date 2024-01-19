package fun.scop.app.isr

import java.lang.management.ManagementFactory

object Logger {
  val threadMXBean = ManagementFactory.getThreadMXBean
  val initCpuTime = threadMXBean.getCurrentThreadCpuTime

  def getWcTimePassed() = {
    val wctime = threadMXBean.getCurrentThreadCpuTime - initCpuTime
    java.util.concurrent.TimeUnit.NANOSECONDS.toSeconds(wctime)
  }

  def log(str: String) = {
    println(s"c ${getWcTimePassed} $str")
  }

}
