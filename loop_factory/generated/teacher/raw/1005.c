int main1(int m,int q){
  int h, k, v;

  h=q;
  k=h;
  v=h;

  while (k-1>=0) {
      if (v+6<h) {
          v = v%4;
      }
      k = k-1;
  }

}
