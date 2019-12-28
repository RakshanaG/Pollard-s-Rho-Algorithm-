import java.math.BigInteger;
import java.util.Random;

public class Main {
    //The function finds the exponentiation of a point
    public static BigInteger[] exp(BigInteger[] a, BigInteger m,BigInteger d, BigInteger p) {
        BigInteger[] b=new BigInteger[2];
        b[0]=new BigInteger("0");
        b[1]=new BigInteger("1");
        for(int i=m.bitLength()-1; i>=0;i--) {
            b=mul(b,b,d,p);
            if(m.testBit(i)){
                b=mul(a,b,d,p);
            }
        }
        return b;
    }
    //The function performs point multiplication between two point on the elliptic curve
    //The formula is ((x1y2+y1x2)/(1+dx1x2y1y2),(y1y2-x1x2)/(1-dx1x2y1y2))
    //A modulus with respect to p is performed to all the arithmetic operations
    public static BigInteger[] mul(BigInteger[] a1,BigInteger[] a2, BigInteger d,BigInteger p) {
        BigInteger[] a3=new BigInteger[2];
        try {
            BigInteger denominator = d.multiply((a1[0]).multiply((a2[0]).multiply((a1[1]).multiply(a2[1])))).mod(p);
            BigInteger x1y2 = (a1[0].multiply(a2[1])).mod(p);
            BigInteger y1x2 = (a1[1].multiply(a2[0])).mod(p);
            BigInteger y1y2 = (a1[1].multiply(a2[1])).mod(p);
            BigInteger x1x2 = (a1[0].multiply(a2[0])).mod(p);
            BigInteger u1 = x1y2.add(y1x2).mod(p);      //x1y1+y1x2
            BigInteger v1 = (new BigInteger("1").add(denominator)).mod(p);      //1+dx1x2y1y2
            BigInteger u2 = y1y2.subtract(x1x2).mod(p);     //y1y2-x1x2
            BigInteger v2 = (new BigInteger("1").subtract(denominator)).mod(p);     //1-dx1x2y1y2
            a3[0] = (u1.multiply(v1.modInverse(p))).mod(p);      //(x1y2+y1x2)/(1+dx1x2y1y2)
            a3[1] = (u2.multiply(v2.modInverse(p))).mod(p);      //(y1y2-x1x2)/(1-dx1x2y1y2)
        }
        catch (Exception e) {
            System.out.println(e.getMessage());
        }
        return a3;
    }
    //The function updates the values of alphak, betak, zk, alpha2k, beta2k, and z2k until zk(x)=z2k(x)
    public static BigInteger[] update_Values(BigInteger[] a, BigInteger[] b, BigInteger[] z, BigInteger alpha,
                                     BigInteger beta,BigInteger d,BigInteger p,BigInteger n) {
        switch ((z[0].mod(new BigInteger("3"))).intValue()) {
            case 0:     //When x-coordinate belongs to group S0
                z=mul(z,b,d,p);
                alpha=alpha.add(new BigInteger("1")).mod(n);
                break;
            case 1:     //When x-coordinate belongs to group S1
                z=mul(z,z,d,p);
                alpha=new BigInteger("2").multiply(alpha).mod(n);
                beta=new BigInteger("2").multiply(beta).mod(n);
                break;
            case 2:     //When x-coordinate belongs to group S2
                z=mul(a,z,d,p);
                beta=beta.add(new BigInteger("1")).mod(n);
                break;
        }
        //The updated values of zk or z2k and alphak or alpha2k and beta or beta2k are returned to the rho function through result array
        BigInteger[] result=new BigInteger[]{z[0],z[1],alpha,beta};
        return result;
    }
    //The function implements the Pollard's Rho Algorithm
    public static BigInteger[] rho(BigInteger[] a,BigInteger[]b, BigInteger d,BigInteger p,BigInteger n) throws ArithmeticException {
        BigInteger alpha,two_alpha,beta,two_beta,m;
        BigInteger[]z = new BigInteger[]{BigInteger.ZERO,BigInteger.ONE};       //Initializing zk to (0,1)
        BigInteger[] two_z=new BigInteger[]{BigInteger.ZERO,BigInteger.ONE};        //Initializing z2k to (0,1)
        long k=0;       //Initializing number of steps to 0
        alpha=BigInteger.ZERO;      //Initializing alphak to 0
        beta=BigInteger.ZERO;       //Initializing betak to 0
        two_alpha=BigInteger.ZERO;      //Initializing alpha2k to 0
        two_beta=BigInteger.ZERO;       //Initializing beta2k to 0
        do {
            BigInteger[] result = update_Values(a,b,z,alpha,beta,d,p,n);    //calculating z(k+1), alpha(k+1) and beta(k+1)
            z[0]=result[0];
            z[1]=result[1];
            alpha=result[2];
            beta=result[3];
            result =update_Values(a,b,two_z,two_alpha,two_beta,d,p,n);      //calculating z(2k+1), alpha(2k+1) and beta(2k+1)
            two_z[0]=result[0];
            two_z[1]=result[1];
            two_alpha=result[2];
            two_beta=result[3];
            result =update_Values(a,b,two_z,two_alpha,two_beta,d,p,n);      //calculating z(2k+2), alpha(2k+2) and beta(2k+2)
            two_z[0]=result[0];
            two_z[1]=result[1];
            two_alpha=result[2];
            two_beta=result[3];
            k++;        //Incrementing the number of steps performed
        }while(!(z[0].equals(two_z[0]) && z[1].equals(two_z[1])));      //The loop is executed until zk(x)!=z2k(x)
        BigInteger beta_diff=two_beta.subtract(beta).mod(n);        //beta2k-betak
        BigInteger alpha_diff=alpha.subtract(two_alpha).mod(n);     //alphak-alpha2k
        BigInteger[] mk=new BigInteger[2];
        try {
            if(alpha_diff.equals(BigInteger.ZERO)) {
                throw new ArithmeticException("alpha_k - alpha_2k is zero -> the Rho method failed for the initialization of z0, alpha0, beta0");
            }
            m=(beta_diff.multiply(alpha_diff.modInverse(n))).mod(n);        //((beta2k-betak)/(alphak-alpha2k))mod(n)
            mk[0]= m;
            mk[1]= BigInteger.valueOf(k);
        }
        catch (Exception e) {
            System.out.println(e);
        }
        return mk;
    }

    public static long check(BigInteger[] a, BigInteger d, BigInteger p, BigInteger n) {
        //Generate random m within the range of 0 to n
        Random r=new Random();
        BigInteger m=new BigInteger(n.bitLength(),r).mod(n);
        BigInteger[] b=exp(a,m,d,p);    //A point on the elliptic curve calculated by the formula b=a^m
        BigInteger[] mk=rho(a,b,d,p,n);     // rho function returns the value of m and k calculated using the rho algorithm; mk[0]=m; mk[1]=k
        try {
            //When the randomly generated m is not equal to the m calculated using the rho function, a runtime exception is thrown
            if(!(m.equals(mk[0]))) {
                throw new RuntimeException("Randomly generated m is not equal to m extracted by rho function");
            }
        }
        catch (Exception e) {
            System.out.println(e);
        }
        return mk[1].longValue();       //The number of steps required to calculate m using rho algorithm is returned.
    }

    public static void main(String[] args) {
        BigInteger p = (new BigInteger("2").pow(16)).subtract(new BigInteger("17"));
        BigInteger d=new BigInteger("154");
        BigInteger[] a=new BigInteger[2];   //A point on the elliptic curve
        BigInteger n=new BigInteger("16339");
        a[0]=new BigInteger("12");
        a[1]=new BigInteger("61833");
        int N=1000;     //Number of times the program must be iterated
        long avg_k=0;       //Average number of steps to find exponent m using Pollard's Rho algorithm
        for (int i=0;i<N;i++) {
            long k = check(a, d, p, n);     //Number of steps taken by the Pollard's Rho Algorithm to find m
            avg_k+=k;
        }
        avg_k/=N;
        System.out.println("Average Number of steps: "+avg_k);
    }
}
