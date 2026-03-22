int main1(){
  int z2b, zvd, at, xy0, x2, qk;

  z2b=(1%34)+5;
  zvd=0;
  at=5;
  xy0=zvd;
  x2=1;
  qk=zvd;

  while (1) {
      if (!(at<=z2b)) {
          break;
      }
      xy0 = xy0*at;
      if (at<z2b) {
          x2 = x2*at;
      }
      qk = qk+(x2%8);
      at = at + 1;
  }

}
