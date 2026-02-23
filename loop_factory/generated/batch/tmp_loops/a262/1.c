int main1(int k,int p){
  int b, w, v, e;

  b=(k%33)+7;
  w=b+3;
  v=b;
  e=-4;

  while (w>b) {
      v = v+1;
      e = e-1;
      v = v*v+v;
  }

}
