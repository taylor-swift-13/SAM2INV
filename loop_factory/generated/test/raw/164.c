int main1(int a,int b,int n,int p){
  int l, i, v, t;

  l=a+11;
  i=0;
  v=i;
  t=b;

  while (v!=0&&t!=0) {
      if (v>t) {
          v = v-t;
      }
      else {
          t = t-v;
      }
      v = v+1;
      t = t-1;
      t = v-t;
      v = v+i;
      t = l;
      v = v+5;
  }

}
