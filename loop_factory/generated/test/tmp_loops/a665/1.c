int main1(int b,int m){
  int l, i, v, w;

  l=(m%36)+19;
  i=0;
  v=l;
  w=-4;

  while (i<l) {
      v = v+1;
      i = i+1;
  }

  while (l<i) {
      v = v+l;
      v = v-v;
      l = l+5;
  }

}
