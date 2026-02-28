int main1(int k,int m){
  int q, u, h, o;

  q=(k%10)+9;
  u=0;
  h=q;
  o=0;

  while (u<q) {
      if (h+6<=q) {
          h = h+6;
      }
      else {
          h = q;
      }
      h = h+1;
  }

}
