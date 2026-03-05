int main199(int w,int k){
  int f4, ap7, xi3, fdl, d;

  f4=(w%29)+19;
  ap7=0;
  xi3=k;
  fdl=w;
  d=-6;

  while (ap7<=f4-1) {
      fdl = fdl/2;
      xi3 = xi3*2;
      xi3 = xi3 - k;
      if ((ap7%3)==0) {
          d = d%2;
      }
      ap7 = ap7 + 1;
  }

}
