int main1(int b,int k){
  int l, i, v, h;

  l=k+20;
  i=l;
  v=b;
  h=b;

  while (i>0) {
      v = v+4;
      h = h+v;
      i = i-1;
  }

  while (v<h) {
      v = v+1;
  }

}
