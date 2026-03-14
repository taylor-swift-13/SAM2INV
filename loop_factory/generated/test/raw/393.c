int main1(int p,int b){
  int g, x1, g1, w, no;

  g=b+19;
  x1=0;
  g1=3;
  w=0;
  no=0;

  while (x1<=g-1) {
      no += 1;
      w += 1;
      if (w>=8) {
          w -= 8;
          g1 += 1;
      }
      x1++;
  }

}
