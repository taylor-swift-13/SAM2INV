int main1(){
  int tj4, a, pbso, oij;

  tj4=(1%10)+20;
  a=0;
  pbso=0;
  oij=0;

  while (1) {
      if (!(a < tj4)) {
          break;
      }
      pbso = pbso + oij * ++a;
      oij += tj4;
      a = tj4;
  }

}
