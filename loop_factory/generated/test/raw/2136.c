int main1(int f){
  int we7f, uk, je, w;

  we7f=(f%32)+9;
  uk=0;
  je=we7f;
  w=f;

  while (1) {
      if (!(uk < we7f)) {
          break;
      }
      uk += 1;
      if (je >= f) {
          je -= f;
          w += f;
      }
      f = f + we7f;
  }

}
