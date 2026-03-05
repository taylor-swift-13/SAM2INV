int main105(int z,int d,int b){
  int dd2, ef0, rr;

  dd2=b*3;
  ef0=dd2;
  rr=8;

  for (; ef0-4>=0; ef0 -= 4) {
      z = z - 1;
      rr = rr + 1;
      rr = rr + 1;
      z = z + ef0;
      if ((ef0%5)==0) {
          b += rr;
      }
  }

}
