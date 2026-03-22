int main1(){
  int c, ey9, l, rub;

  c=1;
  ey9=0;
  l=0;
  rub=1*3;

  while (1) {
      if (!(ey9 < c)) {
          break;
      }
      ey9 = ey9 + 1;
      l = l + rub;
      rub += l;
  }

}
