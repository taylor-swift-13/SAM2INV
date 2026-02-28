int main1(int a,int b){
  int n, i, v, o;

  n=a-7;
  i=0;
  v=6;
  o=-5;

  while (1) {
      v = v+3;
      o = o+3;
      v = v+1;
      o = o-1;
      if (v+7<n) {
          o = o+v;
      }
  }

}
