int main1(){
  int rwf0, uha, va, b;

  rwf0=9;
  uha=0;
  va=0;
  b=8;

  while (1) {
      if (!(uha<rwf0&&b>0)) {
          break;
      }
      uha = uha + 1;
      va += b;
      b = b - 1;
  }

}
