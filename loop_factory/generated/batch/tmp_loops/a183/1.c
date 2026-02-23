int main1(int a,int n){
  int l, u, s, o;

  l=n+23;
  u=l;
  s=n;
  o=n;

  while (s!=0&&o!=0) {
      if (s>o) {
          s = s-o;
      }
      else {
          o = o-s;
      }
      s = s*s+s;
      s = s%6;
  }

}
