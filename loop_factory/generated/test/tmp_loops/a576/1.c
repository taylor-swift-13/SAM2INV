int main1(int b,int k){
  int l, i, v;

  l=61;
  i=l;
  v=b;

  while (i>0) {
      v = v+v;
      i = i/2;
  }

  while (v<l) {
      v = v+1;
  }

}
