int main1(int a){
  int fw, w, p0, x;

  fw=36;
  w=0;
  p0=0;
  x=5;

  while (1) {
      if (!(w<fw&&x>0)) {
          break;
      }
      p0 += x;
      w += 1;
      x--;
  }

}
