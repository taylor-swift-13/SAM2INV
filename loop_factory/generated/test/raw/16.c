int main1(int f){
  int ge, ko, m5n, wi;

  ge=f-9;
  ko=ge;
  m5n=0;
  wi=ko;

  while (1) {
      if (!(m5n<ge)) {
          break;
      }
      if (m5n<ge/2) {
          m5n += 2;
      }
      else {
          m5n += 1;
      }
      f += 2;
      wi += m5n;
  }

}
