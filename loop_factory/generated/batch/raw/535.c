int main1(int k,int n){
  int f, j, v, o;

  f=20;
  j=f;
  v=f;
  o=-4;

  while (j-1>=0) {
      if (v+1<=f) {
          v = v+1;
      }
      else {
          v = f;
      }
      v = v+1;
      o = o+v;
  }

}
