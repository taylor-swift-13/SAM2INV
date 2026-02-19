int main1(int n,int q){
  int l, i, v, w;

  l=(n%17)+19;
  i=0;
  v=-3;
  w=l;

  while (i<l) {
      v = v+3;
      w = w+4;
      i = i+4;
  }

  while (l>0) {
      l = l-1;
  }

}
