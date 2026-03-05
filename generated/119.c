int main119(int d,int j,int a){
  int t, hxzc, i1t, ur, a0, mrm;

  t=(a%37)+12;
  hxzc=0;
  i1t=18;
  ur=0;
  a0=1;
  mrm=0;

  while (1) {
      if (!(i1t>0&&hxzc<t)) {
          break;
      }
      if (i1t<a0) {
          mrm = i1t;
      }
      else {
          mrm = a0;
      }
      a0++;
      ur += mrm;
      hxzc++;
      i1t -= mrm;
  }

}
