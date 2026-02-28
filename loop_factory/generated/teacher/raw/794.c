int main1(int b,int n){
  int w, s, v, l;

  w=(b%11)+8;
  s=w;
  v=-6;
  l=w;

  while (s-1>=0) {
      if (v+3<=w) {
          v = v+3;
      }
      else {
          v = w;
      }
      v = v+2;
  }

}
