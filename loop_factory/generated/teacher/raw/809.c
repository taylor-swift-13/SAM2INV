int main1(int a,int p){
  int v, j, s, h;

  v=(p%17)+7;
  j=0;
  s=0;
  h=0;

  while (s<v) {
      if (s<v/2) {
          h = h+2;
      }
      else {
          h = h-2;
      }
      s = s+1;
      s = s+5;
      h = h+3;
      s = s+2;
  }

}
