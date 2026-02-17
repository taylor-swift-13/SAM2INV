int main1(int a,int k,int m,int q){
  int l, i, v, f, x;

  l=(k%19)+16;
  i=l;
  v=q;
  f=1;
  x=m;

  while (i>0) {
      v = v+f+x;
      v = v+1;
      f = f+x;
      x = v-x;
      f = f+4;
      i = i-1;
  }

}
