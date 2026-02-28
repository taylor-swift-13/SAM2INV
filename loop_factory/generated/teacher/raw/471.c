int main1(int n,int p){
  int k, f, h, o;

  k=27;
  f=0;
  h=k;
  o=k;

  while (1) {
      if (f>=k) {
          break;
      }
      h = h+2;
      f = f+1;
      h = h+1;
      o = o+h;
      if (o+4<k) {
          h = h+f;
      }
  }

}
