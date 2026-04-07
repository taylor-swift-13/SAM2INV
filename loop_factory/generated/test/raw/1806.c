int main1(int i){
  int rf, gh5l, c9, kxk, ye, e5i9;

  rf=i-1;
  gh5l=rf;
  c9=1;
  kxk=1;
  ye=1;
  e5i9=1;

  while (1) {
      if (!(gh5l < rf)) {
          break;
      }
      c9 = c9*3+(e5i9%3)+1;
      gh5l += 1;
      kxk = kxk*2+(c9%7)+2;
      ye = ye*2+(kxk%2)+3;
  }

}
