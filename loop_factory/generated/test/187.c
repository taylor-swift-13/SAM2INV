int main187(int b,int m,int q){
  int n, i, r, v;

  n=m+7;
  i=0;
  r=b;
  v=-5;

  while (i<n) {
      if (r+3<=n) {
          r = r+3;
      }
      else {
          r = n;
      }
      r = r*2;
  }

  while (v-1>=0) {
      r = r+3;
  }

  while (v!=0&&n!=0) {
      if (v>n) {
          v = v-n;
      }
      else {
          n = n-v;
      }
  }


  /*@ assert v == 0&&n!=0; */
}
