int main1(){
  int l, c9, j2c, zu, i, h;

  l=1;
  c9=0;
  j2c=0;
  zu=1;
  i=1;
  h=c9;

  while (1) {
      if (!(zu<=l)) {
          break;
      }
      j2c = j2c + 1;
      i += 2;
      zu = zu + i;
      h = h+zu+zu;
  }

}
