int main1(int n,int p){
  int a, e, v;

  a=(p%12)+6;
  e=0;
  v=-4;

  while (e+1<=a) {
      v = v+3;
      v = v*v+v;
  }

}
