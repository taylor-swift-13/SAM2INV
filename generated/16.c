int main16(int r,int p,int w){
  int io, ntb, f7;

  io=p+22;
  ntb=io;
  f7=r;

  while (1) {
      if (!(ntb<io)) {
          break;
      }
      f7 += 2;
      r = r + 3;
      ntb = ntb + 1;
      p = p+io-ntb;
      w += ntb;
  }

}
