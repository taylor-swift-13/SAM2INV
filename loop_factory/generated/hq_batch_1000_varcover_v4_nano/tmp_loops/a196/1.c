int main1(int b,int k,int p,int q){
  int l, i, v, a, f, t;

  l=64;
  i=l;
  v=(k%40)+10;
  a=(k%30)+6;
  f=k;
  t=p;

  while (v!=0&&a!=0) {
      if (v>a) {
          v = v-a;
      }
      else {
          a = a-v;
      }
      v = v+1;
      a = a+v;
      if (i+6<=l+l) {
          a = a+v;
      }
      else {
          a = f+p;
      }
      a = a+1;
      if (v+6<l) {
          a = a+1;
      }
  }

}
