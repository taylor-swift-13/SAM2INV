int main1(){
  int ny, vvw, q, jo;

  ny=(1%25)+7;
  vvw=0;
  q=0;
  jo=ny;

  while (1) {
      if (!(vvw < ny)) {
          break;
      }
      jo = jo + ny;
      q = (vvw = vvw + 1) % 2;
      vvw = ny;
  }

}
