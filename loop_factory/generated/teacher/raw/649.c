int main1(int b,int k){
  int h, s, p, v, r, a;

  h=(k%27)+11;
  s=h;
  p=8;
  v=-2;
  r=s;
  a=h;

  while (a<=h) {
      p = p+v;
      v = v+r;
      r = r+6;
      a = a+1;
      p = p+s;
  }

}
