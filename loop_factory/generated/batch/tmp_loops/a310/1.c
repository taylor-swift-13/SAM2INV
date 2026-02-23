int main1(int a,int p){
  int n, d, h;

  n=p;
  d=1;
  h=n;

  while (d<=n/3) {
      h = h*h;
      h = h%2;
      d = d*3;
  }

}
