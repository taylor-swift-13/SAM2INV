int main11(int b,int m,int p){
  int r, k, h;

  r=b-9;
  k=r;
  h=m;

  while (k>=2) {
      if (k*k<=r+5) {
          h = h*h;
      }
      h = h+h;
      k = k-2;
  }

}
