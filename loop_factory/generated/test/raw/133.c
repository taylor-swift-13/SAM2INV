int main1(){
  int l4, n3, mx;

  l4=1;
  n3=0;
  mx=0;

  while (n3<l4) {
      if (n3%2==0) {
          if (mx>0) {
              mx -= 1;
              mx++;
          }
      }
      else {
          if (mx>0) {
              mx -= 1;
              mx++;
          }
      }
      n3 += 1;
      mx = mx + mx;
      mx = n3+l4;
  }

}
