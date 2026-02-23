int main1(int a,int n){
  int s, g, v, d;

  s=n+20;
  g=0;
  v=s;
  d=a;

  while (g<s) {
      v = v+1;
      d = d+1;
      v = v+d+d;
  }

}
