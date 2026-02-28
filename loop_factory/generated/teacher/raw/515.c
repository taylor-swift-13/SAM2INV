int main1(int b,int k){
  int h, s, p, v;

  h=k;
  s=2;
  p=-8;
  v=h;

  while (1) {
      if (s>=h) {
          break;
      }
      p = p+2;
      s = s+1;
      p = p+1;
      v = v+p;
  }

}
