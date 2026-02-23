int main1(int a,int p){
  int v, g, h, n;

  v=a+10;
  g=v+4;
  h=p;
  n=1;

  while (h!=0&&n!=0) {
      if (h>n) {
          h = h-n;
      }
      else {
          n = n-h;
      }
  }

}
