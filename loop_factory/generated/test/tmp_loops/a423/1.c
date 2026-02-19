int main1(int k,int m){
  int l, i, v, b;

  l=(k%17)+4;
  i=l;
  v=l;
  b=-6;

  while (i>0) {
      v = v*3;
      b = b/3;
      v = v+1;
  }

  while (l<v) {
      i = i*2;
      b = b/2;
      i = i+1;
  }

}
