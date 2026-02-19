int main1(int k,int n){
  int l, i, v, w;

  l=17;
  i=0;
  v=l;
  w=k;

  while (i<l) {
      v = v+w+w;
      i = i+1;
  }

  while (l<v) {
      w = w+w;
      l = l+2;
  }

}
