int main1(int a,int n,int p,int q){
  int l, i, v, h, g;

  l=q;
  i=0;
  v=q;
  h=a;
  g=i;

  while (i<l) {
      if (i%5==2) {
          v = v+1;
      }
      else {
          h = h+1;
      }
      if (i%5==3) {
          g = g+1;
      }
      else {
      }
      v = v+2;
      h = h+v;
      g = g+h;
      h = h+g;
      if ((i%2)==0) {
          g = g+1;
      }
  }

}
