int main1(int p,int q){
  int l, i, v;

  l=q+6;
  i=0;
  v=l;

  while (i<l) {
      v = v+v;
      v = v+i;
      i = i+1;
  }

  while (v<l) {
      i = i+i;
      v = v*3;
  }

}
