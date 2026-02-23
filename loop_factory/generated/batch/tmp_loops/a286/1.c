int main1(int n,int p){
  int s, c, u;

  s=n-8;
  c=0;
  u=s;

  while (c<=s-1) {
      u = u*2;
      if (u+4<s) {
          u = u+(-6);
      }
      c = c+1;
  }

}
