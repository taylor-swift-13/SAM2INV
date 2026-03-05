int main1(int n,int y){
  int dn, kb, ux8;

  dn=(n%7)+11;
  kb=0;
  ux8=1;

  while (kb+1<=dn) {
      if (ux8==1) {
          ux8 = 2;
      }
      else {
          if (ux8==2) {
              ux8 = 1;
          }
      }
      n = n + ux8;
      y = y + ux8;
  }

}
