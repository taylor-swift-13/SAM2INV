int main1(){
  int nnj, c, h;

  nnj=0;
  c=(1%28)+10;
  h=-4;

  while (1) {
      if (!(c>nnj)) {
          break;
      }
      c -= nnj;
      h = h + c;
      nnj += 1;
      h = h*3;
  }

}
