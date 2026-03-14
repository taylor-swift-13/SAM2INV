int main1(int b,int w){
  int r6ij, ryl, sa7, j6hv, tl;

  r6ij=b-9;
  ryl=0;
  sa7=0;
  j6hv=1;
  tl=b;

  while (sa7+4<=r6ij+4-1) {
      j6hv = sa7+1;
      sa7 += 4;
      tl = tl + ryl;
  }

  while (1) {
      if (!(sa7+4<=ryl)) {
          break;
      }
      j6hv = j6hv+r6ij*sa7;
      b = b + sa7;
      ryl = (sa7+4)-1;
  }

}
