int main1(int a,int q){
  int l, i, v, d;

  l=(q%24)+11;
  i=l;
  v=0;
  d=l;

  while (i>0) {
      v = v*4;
      d = d/4;
      v = v+1;
  }

  while (d<v) {
      i = i+1;
      d = d+1;
  }

}
