int main1(int m,int n){
  int e, s, q, w;

  e=65;
  s=1;
  q=4;
  w=n;

  while (s+1<=e) {
      if (s<e/2) {
          q = q+w;
      }
      else {
          q = q*w;
      }
      q = q+w;
      w = w+w;
  }

}
