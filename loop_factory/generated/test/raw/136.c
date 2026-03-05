int main1(){
  int l, un0, a;

  l=(1%33)+4;
  un0=0;
  a=0;

  while (un0<l) {
      if (un0%2==0) {
          if (a>0) {
              a -= 1;
              a++;
          }
      }
      else {
          if (a>0) {
              a -= 1;
              a++;
          }
      }
      un0 += 1;
      a = a - a;
  }

}
