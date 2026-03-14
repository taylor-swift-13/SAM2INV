int main1(){
  int tw, i, louv, dw4;

  tw=46;
  i=1;
  louv=0;
  dw4=2;

  while (1) {
      if (!(i<tw)) {
          break;
      }
      louv++;
      dw4 = dw4 + tw;
      i = 2*i;
      dw4 = dw4 + dw4;
  }

}
