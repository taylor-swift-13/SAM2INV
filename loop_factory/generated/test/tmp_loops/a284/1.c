int main1(int p,int q){
  int l, i, v, f;

  l=(q%32)+20;
  i=0;
  v=-5;
  f=l;

  while (i<l) {
      v = v+4;
      f = f+4;
      i = i+1;
  }

  while (l<f) {
      i = i+4;
      v = v+2;
      l = l+1;
  }

}
