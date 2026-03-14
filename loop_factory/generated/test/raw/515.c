int main1(){
  int mhzk, r, m8;

  mhzk=55;
  r=mhzk;
  m8=mhzk;

  while (1) {
      if (!(r>=1)) {
          break;
      }
      m8 += r;
      r--;
  }

}
