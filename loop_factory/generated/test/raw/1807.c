int main1(){
  int e9, c8, to;

  e9=(1%20)+1;
  c8=(1%25)+1;
  to=0;

  while (c8!=0) {
      if (c8%2==1) {
          to += e9;
          c8 = c8 - 1;
      }
      else {
      }
      e9 = 2*e9;
      c8 = c8/2;
  }

}
