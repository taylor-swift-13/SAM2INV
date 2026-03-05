int main189(int b){
  int e6, p0, ir, qo, zn, s0c0;

  e6=b+11;
  p0=e6+6;
  ir=50;
  qo=0;
  zn=p0;
  s0c0=p0;

  while (ir>0) {
      qo += 2;
      ir -= 2;
      s0c0 = s0c0+e6-p0;
      b = b+(qo%5);
      zn = zn*2;
      s0c0 += zn;
  }

}
