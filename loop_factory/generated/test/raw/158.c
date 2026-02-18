int main1(int a,int b,int n,int p){
  int l, i, v, f, t;

  l=68;
  i=0;
  v=3;
  f=8;
  t=p;

  while (i<l) {
      v = v+1;
      f = f+v;
      f = f+i;
      t = v-t;
      i = i+1;
  }

}
