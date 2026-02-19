int main1(int b,int q){
  int l, i, v;

  l=(q%36)+10;
  i=1;
  v=3;

  while (i<l) {
      v = v+v;
      i = i*3;
  }

  while (l>0) {
      v = v-v;
      l = l-1;
  }

}
