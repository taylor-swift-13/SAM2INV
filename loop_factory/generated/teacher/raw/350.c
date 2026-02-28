int main1(int a,int q){
  int n, w, h;

  n=q+10;
  w=0;
  h=q;

  while (w<n) {
      if (a<w+1) {
          h = h+1;
      }
      w = w+1;
  }

}
